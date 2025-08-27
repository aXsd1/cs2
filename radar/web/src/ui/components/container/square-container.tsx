import { Box, SxProps, Theme } from "@mui/material";
import React, { useContext } from "react";


const SquareSizeContext = React.createContext<number>(1);
export default React.memo((props: {
    children: React.ReactNode,
    squareSize: number,
    sx?: SxProps<Theme>,
}) => {
    return (
        <Box
            sx={props.sx}
            style={{
                width: `${props.squareSize}px`,
                height: `${props.squareSize}px`,
            } as any}
        >
            <SquareSizeContext.Provider value={props.squareSize}>
                {props.children}
            </SquareSizeContext.Provider>
        </Box>
    )
});

export const useSquareSize = () => useContext(SquareSizeContext);